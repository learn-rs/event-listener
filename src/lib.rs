use std::sync::atomic::{AtomicUsize, Ordering, AtomicPtr};
use std::sync::{Mutex, MutexGuard, Arc};
use std::cell::{UnsafeCell, Cell};
use std::ptr::NonNull;
use std::task::{Waker, Context, Poll};
use std::thread::Thread;
use std::mem;
use std::ptr;
use std::ops::{Deref, DerefMut};
use crate::State::Polling;
use std::panic::{UnwindSafe, RefUnwindSafe};
use std::time::{Instant, Duration};
use std::mem::ManuallyDrop;
use std::fmt::Formatter;
use std::future::Future;
use std::pin::Pin;

/// Inner state of [`Event`]
struct Inner {
    /// The number of notified entries, or `usize::MAX` if all of them have been notified
    ///
    /// If there are no entries, this value is set to `usize::MAX`
    notified: AtomicUsize,

    /// A linked list holding registered listeners
    list: Mutex<List>,

    /// A single cached list entry to avoid allocations on the fast path of the insertion.
    cache: UnsafeCell<Entry>
}

impl Inner {
    /// Locks the list
    fn lock(&self) -> ListGuard<'_> {
        ListGuard {
            inner: self,
            guard: self.list.lock().unwrap()
        }
    }

    /// Returns the pointer to the single cached list entry
    fn cache_ptr(&self) -> NonNull<Entry> {
        unsafe { NonNull::new_unchecked(self.cache.get()) }
    }
}

pub struct Event {
    /// A pointer to heap-allocated inner state
    ///
    /// This pointer is initially null and gets lazily initialized on first use. Semantically,
    /// it is an `Arc<Inner>` so it's important to keep in mind that it contributes to the [`Arc`]'s
    /// reference count
    inner: AtomicPtr<Inner>
}

unsafe impl Send for Event {}
unsafe impl Sync for Event {}

impl UnwindSafe for Event {}
impl RefUnwindSafe for Event {}

impl Event {

    /// Creates a new [`Event`]
    #[inline]
    pub const fn new() -> Event {
        Event {
            inner: AtomicPtr::new(ptr::null_mut())
        }
    }

    /// Returns a guard listening for a notification
    ///
    /// This method emits a `SeqCst` fence after registering a listener
    #[cold]
    pub fn listen(&self) -> EventListener {
        let inner = self.inner();
        let listener = EventListener {
            inner: unsafe { Arc::clone(&ManuallyDrop::new(Arc::from_raw(inner)))},
            entry: Some(inner.lock().insert(inner.cache_ptr()))
        };

        full_fence();
        listener
    }

    #[inline]
    pub fn notify(&self, n: usize) {
        full_fence();
        self.notify_relaxed(n);
    }

    #[inline]
    pub fn notify_relaxed(&self, n: usize) {
        if let Some(inner) = self.try_inner() {
            if inner.notified.load(Ordering::Acquire) < n {
                inner.lock().notify(n);
            }
        }
    }

    #[inline]
    pub fn notify_additional(&self, n: usize) {
        full_fence();
        self.notify_additional_relaxed(n);
    }

    #[inline]
    pub fn notify_additional_relaxed(&self, n: usize) {
        if let Some(inner) = self.try_inner() {
            if inner.notified.load(Ordering::Acquire) < usize::MAX {
                inner.lock().notify_additional(n);
            }
        }
    }

    #[inline]
    fn try_inner(&self) -> Option<&Inner> {
        let inner = self.inner.load(Ordering::Acquire);
        unsafe { inner.as_ref() }
    }

    fn inner(&self) -> &Inner {
        let mut inner = self.inner.load(Ordering::Acquire);

        if inner.is_null() {
            let new = Arc::new(Inner {
                notified: AtomicUsize::new(usize::MAX),
                list: std::sync::Mutex::new(List {
                    head: None,
                    tail: None,
                    start: None,
                    len: 0,
                    notified: 0,
                    cache_used: false
                }),
                cache: UnsafeCell::new(Entry {
                    state: Cell::new(State::Created),
                    prev: Cell::new(None),
                    next: Cell::new(None)
                })
            });

            let new = Arc::into_raw(new) as *mut Inner;
            inner = self.inner.compare_and_swap(inner, new, Ordering::AcqRel);
            if inner.is_null() {
                inner = new;
            } else {
                unsafe {
                    drop(Arc::from_raw(new));
                }
            }
        }

        unsafe { &*inner }
    }
}

impl Drop for Event {
    #[inline]
    fn drop(&mut self) {
        let inner: *mut Inner = *self.inner.get_mut();
        if !inner.is_null() {
            unsafe {
                drop(Arc::from_raw(inner));
            }
        }
    }
}

impl std::fmt::Debug for Event {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.pad("Event { .. }")
    }
}

impl Default for Event {
    fn default() -> Self {
        Event::new()
    }
}

/// A guard waiting for a notification from an [`Event`]
///
/// There are two ways for a listener to wait for a notification
///
/// 1. In an asynchronous manner using `.await`
/// 2. In a blocking manner by calling [`EventListener::wait()`] on it
///
/// If a notified listener is dropped without receiving a notification, dropping
/// will notify another active listener. Whether one *additional* listener will be
/// notified depends on what kind of notification was delivered
///
pub struct EventListener {
    /// A reference to [`Event`]'s inner state
    inner: Arc<Inner>,

    /// A pointer to this listener's entry in the linked list
    entry: Option<NonNull<Entry>>
}

unsafe impl Send for EventListener {}
unsafe impl Sync for EventListener {}

impl UnwindSafe for EventListener {}
impl RefUnwindSafe for EventListener {}

impl EventListener {

    pub fn wait(self) {
        self.wait_internal(None);
    }

    pub fn wait_timeout(self, timeout: Duration) -> bool {
        self.wait_internal(Some(Instant::now() + timeout))
    }

    pub fn wait_deadline(self, deadline: Instant) -> bool {
        self.wait_internal(Some(deadline))
    }

    pub fn discard(mut self) -> bool {
        if let Some(entry) = self.entry.take() {
            let mut list = self.inner.lock();
            if let State::Notified(_) = list.remove(entry, self.inner.cache_ptr()) {
                return true;
            }
        }
        false
    }

    pub fn listens_to(&self, event: &Event) -> bool {
        ptr::eq::<Inner>(&*self.inner, event.inner.load(Ordering::Acquire))
    }

    pub fn same_event(&self, other: &EventListener) -> bool {
        ptr::eq::<Inner>(&*self.inner, &*other.inner)
    }


    fn wait_internal(mut self, deadline: Option<Instant>) -> bool {
        let entry = match self.entry.take() {
            None => unreachable!("cannot wait twice on an `EventListener`"),
            Some(entry) => entry,
        };

        // Set this lisntener's state to `Waiting`
        {
            let mut list = self.inner.lock();
            let e = unsafe { entry.as_ref() };

            match e.state.replace(State::Notified(false)) {
                State::Notified(_) => {
                    list.remove(entry, self.inner.cache_ptr());
                    return true;
                }
                _ => e.state.set(State::Waiting(std::thread::current()))
            }
        }

        loop {
            match deadline {
                None => std::thread::park(),
                Some(dealine) => {
                    let now = Instant::now();
                    if now >= deadline {
                        return self.inner.lock().remove(entry, self.inner.cache_ptr())
                            .is_notified();
                    }

                    std::thread::park_timeout(deadline - now);
                }
            }

            let mut list = self.inner.lock();
            let e = unsafe { entry.as_ref() };

            match e.state.replace(State::Notified(false)) {
                State::Notified(_) => {
                    list.remove(entry, self.inner.cache_ptr());
                    return true;
                }
                state => e.state.set(state)
            }
        }
    }
}

impl std::fmt::Debug for EventListener {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.pad("EventListener { .. }")
    }
}

impl Drop for EventListener {
    fn drop(&mut self) {
        if let Some(entry) = self.entry.take() {
            let mut list = self.inner.lock();
            if let State::Notified(additional) = list.remove(entry, self.inner.cache_ptr()) {
                if additional {
                    list.notify_additional(1);
                } else {
                    list.notify(1);
                }
            }
        }
    }
}

impl Future for EventListener {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut list = self.inner.lock();

        let entry = match self.entry {
            None => unreachable!(cannot poll a completed `EventListener` future),
            Some(entry) => entry
        };

        let state = unsafe {
            &entry.as_ref().state
        };

        match state.replace(State::Notified(false)) {
            State::Notified(_) => {
                list.remove(entry, self.inner.cache_ptr());
                drop(list);
                self.entry = None;
                return Poll::Ready(());
            }
            State::Created => {
                state.set(State::Polling(cx.waker().clone()));
            }
            State::Polling(w) => {
                if w.will_wake(cx.waker()) {
                    state.set(State::Polling(w));
                } else {
                    state.set(State::Polling(cx.waker().clone()));
                }
            }
            State::Waiting(_) => {
                unreachable!("cannot poll and wait on `EventListener` at the same time")
            }
        }
        Poll::Pending
    }
}

/// A guard holding the linked list locked
struct ListGuard<'a> {
    /// A reference to [`Event`]'s inner state
    inner: &'a Inner,

    /// The actual guard that acquired the linked list
    guard: MutexGuard<'a, List>
}

impl Drop for ListGuard<'_> {
    fn drop(&mut self) {
        let list = &mut **self;

        // Update the atomic `notified` counter
        let notified = if list.notified < list.len {
            list.notified
        } else {
            usize::MAX
        };
        self.inner.notified.store(notified, Ordering::Release)
    }
}

impl Deref for ListGuard<'_> {
    type Target = List;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &*self.guard
    }
}

impl DerefMut for ListGuard<'_> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.guard
    }
}

/// The state of a listener
enum State {
    /// It has just been created
    Created,

    /// It has received a notification
    ///
    /// The `bool` is `true` if this was an `additional` notification
    Notified(bool),

    /// An async task is polling it
    Polling(Waker),

    /// A thread is blocked on it
    Waiting(Thread),
}

impl State {
    /// Returns `true` if this is the `Notified` state
    #[inline]
    fn is_notified(&self) -> bool {
        match self {
            State::Notified(_) => true,
            _ => false
        }
    }
}

/// A entry representing a registered listener
struct Entry {
    /// The state of this listener
    state: Cell<State>,

    /// Previous entry in the linked list
    prev: Cell<Option<NonNull<Entry>>>,

    /// Next entry in the linked list
    next: Cell<Option<NonNull<Entry>>>
}

/// A linked list of entries
struct List {
    /// First entry in the list
    head: Option<NonNull<Entry>>,

    /// Last entry in the list
    tail: Option<NonNull<Entry>>,

    /// The first unnotified entry in the list
    start: Option<NonNull<Entry>>,

    /// Total number of entries in the list
    len: usize,

    /// The number of notified entries in the list
    notified: usize,

    /// Whether the cached entry is used
    cache_used: bool,
}

impl List {

    /// Inserts a new entry into the list
    fn insert(&mut self, cache: NonNull<Entry>) -> NonNull<Entry> {
        unsafe {
            let entry = Entry {
                state: Cell::new(State::Created),
                prev: Cell::new(self.tail),
                next: Cell::new(None)
            };

            let entry = if self.cache_used {
                // Allocate an entry that is going to become the new tail
                NonNull::new_unchecked(Box::into_raw(Box::new(entry)))
            } else {
                // No need to allocate - we can use the cached entry
                self.cache_used = true;
                cache.as_ptr().write(entry);
                cache
            };

            // Replace the tail with the new entry
            match mem::replace(&mut self.tail, Some(entry)) {
                None => self.head = Some(entry),
                Some(t) => t.as_ref().next.set(Some(entry))
            }

            // If there were no unnotified entries, this one is the first now
            if self.start.is_none() {
                self.start = self.tail;
            }

            // Bump the entry count
            self.len += 1;

            entry
        }
    }

    /// Removes an entry from the list and returns it state
    fn remove(&mut self, entry: NonNull<Entry>, cache: NonNull<Entry>) -> State {
        unsafe {
            let prev = entry.as_ref().prev.get();
            let next = entry.as_ref().next.get();

            // Unlink from the previous entry
            match prev {
                None => self.head = next,
                Some(p) => p.as_ref().next.set(next)
            }

            // Unlink from the next entry
            match next {
                None => self.tail = prev,
                Some(n) => n.as_ref().prev.set(prev)
            }

            // If this was the first unnotified entry, move the pointer to the next one
            if self.start == Some(entry) {
                self.start = next;
            }

            // Extract the state
            let state = if ptr::eq(entry.as_ptr(), cache.as_ptr()) {
                // Free the cached entry
                self.cache_used = false;
                entry.as_ref().state.replace(State::Created)
            } else {
                // Deallocate the entry
                Box::from_raw(entry.as_ptr()).state.into_inner()
            };

            // Update the counters
            if state.is_notified() {
                self.notified -= 1;
            }
            self.len -= 1;

            state
        }
    }

    // Notifies a number of entries
    #[cold]
    fn notify(&mut self, mut n: usize) {
        if n <= self.notified {
            return;
        }
        n -= self.notified;
        while n > 0 {
            n -= 1;

            // Notify the first unnotified entry
            match self.start {
                None => break,
                Some(e) => {
                    // Get the entry and move the pointer forward
                    let e = unsafe { e.as_ref() };
                    self.start = e.next.get();

                    // Set the state of this entry to `Notified` an notify
                    match e.state.replace(State::Notified(false)) {
                        State::Notified(_) => {},
                        State::Created => {},
                        State::Polling(w) => w.wake(),
                        State::Waiting(t) => t.unpark()
                    }

                    // Update the counter
                    self.notified += 1;
                }
            }
        }
    }

    /// Notifies a number of additional entries
    #[cold]
    fn notify_additional(&mut self, mut n: usize) {
        while n > 0 {

            // Notify the first unnotified entry
            match self.start {
                None => break,
                Some(e) => {
                    // Get the entry and move the pointer forward
                    let e = unsafe { e.as_ref() };
                    self.start = e.next.get();

                    // Set the state of this entry to `Notified` and notify
                    match e.state.replace(State::Notified(true)) {
                        State::Notified(_) => {},
                        State::Created => {},
                        State::Polling(w) => w.wake(),
                        State::Waiting(t) => t.unpark()
                    }

                    // Update the counter
                    self.notified += 1;
                }
            }
        }
    }
}

/// Equvalent to `atomic::fence(Ordering::SeqCst)`, but in some cases faster
#[inline]
fn full_fence() {
    // HACK(stjepang): On x86 architectures there are two different ways of executing
    // a `SeqCst` fence.
    //
    // 1. `atomic::fence(SeqCst)`, which compiles into a `mfence` instruction.
    // 2. `_.compare_and_swap(_, _, SeqCst)`, which compiles into a `lock cmpxchg` instruction.
    //
    // Both instructions have the effect of a full barrier, but empirical benchmarks have shown
    // that the second one is sometimes a bit faster.
    //
    // The ideal solution here would be to use inline assembly, but we're instead creating a
    // temporary atomic variable and compare-and-exchanging its value. No sane compiler to
    // x86 platforms is going to optimize this away.
    if cfg!(any(target_arch = "x86", target_arch = "x86_64")) {
        let a = AtomicUsize::new(0);
        a.compare_and_swap(0, 1, Ordering::SeqCst);
    } else {
        std::sync::atomic::fence(Ordering::SeqCst);
    }
}