
## 2026-07-07 - [Cleanup redundant map_err in mir/dumper.rs]

**Learning:** The clippy warning `clippy::useless_conversion` highlighted an unnecessary `.map_err(Into::into)` call in `src/mir/dumper.rs` because the `write!` macro already returned an `std::fmt::Error`, making the conversion redundant.

**Action:** Removed `.map_err(Into::into)` to clean up the code and resolve the warning. Confirmed tests and clippy still pass successfully.
