#ifndef _STDATOMIC_H
#define _STDATOMIC_H

#define atomic_init(obj, value) (*(obj) = (value))
#define atomic_load(obj) __atomic_load_n(obj, 5)
#define atomic_store(obj, value) __atomic_store_n(obj, value, 5)
#define atomic_exchange(obj, value) __atomic_exchange_n(obj, value, 5)

#define atomic_load_explicit(obj, order) __atomic_load_n(obj, order)
#define atomic_store_explicit(obj, value, order) __atomic_store_n(obj, value, order)
#define atomic_exchange_explicit(obj, value, order) __atomic_exchange_n(obj, value, order)

#define atomic_fetch_add(obj, val) __atomic_fetch_add(obj, val, 5)
#define atomic_fetch_sub(obj, val) __atomic_fetch_sub(obj, val, 5)
#define atomic_fetch_or(obj, val)  __atomic_fetch_or(obj, val, 5)
#define atomic_fetch_xor(obj, val) __atomic_fetch_xor(obj, val, 5)
#define atomic_fetch_and(obj, val) __atomic_fetch_and(obj, val, 5)

#define atomic_fetch_add_explicit(obj, val, order) __atomic_fetch_add(obj, val, order)
#define atomic_fetch_sub_explicit(obj, val, order) __atomic_fetch_sub(obj, val, order)
#define atomic_fetch_or_explicit(obj, val, order)  __atomic_fetch_or(obj, val, order)
#define atomic_fetch_xor_explicit(obj, val, order) __atomic_fetch_xor(obj, val, order)
#define atomic_fetch_and_explicit(obj, val, order) __atomic_fetch_and(obj, val, order)

#define atomic_compare_exchange_weak(obj, expected, desired) \
    __atomic_compare_exchange_n(obj, expected, desired, 1, 5, 5)

#define atomic_compare_exchange_strong(obj, expected, desired) \
    __atomic_compare_exchange_n(obj, expected, desired, 0, 5, 5)

#define atomic_compare_exchange_weak_explicit(obj, expected, desired, succ, fail) \
    __atomic_compare_exchange_n(obj, expected, desired, 1, succ, fail)

#define atomic_compare_exchange_strong_explicit(obj, expected, desired, succ, fail) \
    __atomic_compare_exchange_n(obj, expected, desired, 0, succ, fail)

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
