/// No reason for this number as of now.
pub const DEFAULT_INITIAL_CAPACITY: usize = 8;

/// When the approximate load factor reaches `COLLECT_LOAD_FACTOR`, we remove
/// all the expired pointers and then consider resizing.
pub const COLLECT_LOAD_FACTOR: f32 = 0.9;

/// If, after collection, the load factor is above `GROW_LOAD_FACTOR`, we grow.
pub const GROW_LOAD_FACTOR: f32 = 0.75;

/// If, after collection, the load factor is below `SHRINK_LOAD_FACTOR`, we shrink.
pub const SHRINK_LOAD_FACTOR: f32 = 0.25;


