Module Type Basic.

    Parameter expr bexpr var glob val : Set.
    Parameter store : Set.
    Parameter store_init : store.
    Parameter heap : Set.
    Parameter heap_init : heap.
    Parameter load : store -> var -> val.
    Parameter update : store -> var -> val -> store.
    Parameter read : heap -> glob -> val.
    Parameter write : heap -> glob -> val -> heap.
    Parameter eval : expr -> store -> val.
    Parameter evalb : bexpr -> store -> bool.

End Basic.