//! A simple logger for verbose output.

/// A logger that prints messages only when verbose mode is enabled.
#[derive(Debug, Clone, Copy)]
pub struct Logger {
    verbose: bool,
}

impl Logger {
    /// Creates a new `Logger`.
    ///
    /// # Arguments
    ///
    /// * `verbose` - Whether verbose mode is enabled.
    ///
    /// # Returns
    ///
    /// A new `Logger` instance.
    pub fn new(verbose: bool) -> Self {
        Self { verbose }
    }

    /// Logs a message if verbose mode is enabled.
    ///
    /// # Arguments
    ///
    /// * `msg` - The message to log.
    pub fn log(&self, msg: &str) {
        if self.verbose {
            eprintln!("[VERBOSE] {}", msg);
        }
    }
}
