use std::num::NonZeroU32;
use vector_map::VecMap;

pub type ProductId = u32;

pub struct Inventory {
    /// Every product in inventory must have a non-zero quantity
    pub inner: VecMap<ProductId, NonZeroU32>,
}

impl Inventory {
    pub fn update(&mut self, id: ProductId, new_quantity: NonZeroU32) {
        self.inner.insert(id, new_quantity);
    }

    pub fn get(&self, id: &ProductId) -> Option<NonZeroU32> {
        self.inner.get(id).cloned()
    }
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(100)]
fn check_safe_update() {
    let mut inventory = Inventory {
        inner: VecMap::new(),
    };

    let id: ProductId = kani::any();
    let quantity: NonZeroU32 = kani::any();
    assert!(
        quantity.get() != 0,
        "NonZeroU32 is internally a u32 but it should never be 0."
    );

    inventory.update(id, quantity);
    assert!(inventory.get(&id).unwrap() == quantity);
}
