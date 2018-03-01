use std::rc;
use std::sync;

/// Interface for elements that can be stored in a weak hash table.
pub trait WeakElement {
    /// The type at which a weak element can be viewed.
    ///
    /// For example, for `rc::Weak<T>`, this will be `rc::Rc<T>`.
    type Strong;

    /// Constructs a new weak element from a strong view.
    fn new(view: &Self::Strong) -> Self;

    /// Acquires a strong version of the weak element.
    fn view(&self) -> Option<Self::Strong>;

    /// Is the given weak element expired?
    fn expired(&self) -> bool {
        self.view().is_none()
    }
}

impl<T> WeakElement for rc::Weak<T> {
    type Strong = rc::Rc<T>;

    fn new(view: &Self::Strong) -> Self {
        rc::Rc::<T>::downgrade(view)
    }

    fn view(&self) -> Option<Self::Strong> {
        self.upgrade()
    }
}

impl<T> WeakElement for rc::Rc<T> {
    type Strong = rc::Rc<T>;

    fn new(view: &Self::Strong) -> Self {
        view.clone()
    }

    fn view(&self) -> Option<Self::Strong> {
        Some(self.clone())
    }

    fn expired(&self) -> bool {
        false
    }
}

impl<T> WeakElement for sync::Weak<T> {
    type Strong = sync::Arc<T>;

    fn new(view: &Self::Strong) -> Self {
        sync::Arc::<T>::downgrade(view)
    }

    fn view(&self) -> Option<Self::Strong> {
        self.upgrade()
    }
}

impl<T> WeakElement for sync::Arc<T> {
    type Strong = sync::Arc<T>;

    fn new(view: &Self::Strong) -> Self {
        view.clone()
    }

    fn view(&self) -> Option<Self::Strong> {
        Some(self.clone())
    }

    fn expired(&self) -> bool {
        false
    }
}

impl<T0, T1> WeakElement for (T0, T1)
    where T0: WeakElement,
          T1: WeakElement
{
    type Strong = (T0::Strong, T1::Strong);

    fn new(view: &Self::Strong) -> Self {
        (T0::new(&view.0), T1::new(&view.1))
    }

    fn view(&self) -> Option<Self::Strong> {
        self.0.view().and_then(|view0|
            self.1.view().and_then(|view1|
                Some((view0, view1))))
    }
}

impl<T0, T1, T2> WeakElement for (T0, T1, T2)
    where T0: WeakElement,
          T1: WeakElement,
          T2: WeakElement
{
    type Strong = (T0::Strong, T1::Strong, T2::Strong);

    fn new(view: &Self::Strong) -> Self {
        (T0::new(&view.0), T1::new(&view.1), T2::new(&view.2))
    }

    fn view(&self) -> Option<Self::Strong> {
        self.0.view().and_then(|view0|
            self.1.view().and_then(|view1|
                self.2.view().and_then(|view2|
                    Some((view0, view1, view2)))))
    }
}

impl<T0, T1, T2, T3> WeakElement for (T0, T1, T2, T3)
    where T0: WeakElement,
          T1: WeakElement,
          T2: WeakElement,
          T3: WeakElement
{
    type Strong = (T0::Strong, T1::Strong, T2::Strong, T3::Strong);

    fn new(view: &Self::Strong) -> Self {
        (T0::new(&view.0), T1::new(&view.1), T2::new(&view.2), T3::new(&view.3))
    }

    fn view(&self) -> Option<Self::Strong> {
        self.0.view().and_then(|view0|
            self.1.view().and_then(|view1|
                self.2.view().and_then(|view2|
                    self.3.view().and_then(|view3|
                        Some((view0, view1, view2, view3))))))
    }
}

/// We can own a value as part of a `WeakElement`, provided it's `Clone`.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Strong<T: Clone>(T);

impl<T: Clone> WeakElement for Strong<T> {
    type Strong = T;

    fn new(view: &Self::Strong) -> Self {
        Strong(view.clone())
    }

    fn view(&self) -> Option<Self::Strong> {
        Some(self.0.clone())
    }

    fn expired(&self) -> bool {
        false
    }
}
