#ifndef _STDATOMIC_H
#define _STDATOMIC_H

#define atomic_init(obj, value) (*(obj) = (value))
#define atomic_load(obj) (*(obj))
#define atomic_store(obj, value) (*(obj) = (value))

#define atomic_load_explicit(obj, order) (*(obj))
#define atomic_store_explicit(obj, value, order) (*(obj) = (value))

// Memory order constants (dummy for now)
typedef enum memory_order {
    memory_order_relaxed,
    memory_order_consume,
    memory_order_acquire,
    memory_order_release,
    memory_order_acq_rel,
    memory_order_seq_cst
} memory_order;

#endif /* _STDATOMIC_H */
