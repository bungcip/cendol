//! Error Recovery System
//!
//! This module provides a centralized error recovery system for the parser.
//! It defines strategies for handling parse errors and attempting to continue
//! parsing when recoverable errors occur.

use crate::diagnostic::ParseError;
use crate::lexer::TokenKind;

/// Error recovery strategies for handling parse failures
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecoveryStrategy {
    /// Panic on any error - stop parsing immediately
    Panic,
    /// Skip the problematic token and continue
    Skip,
    /// Insert a synthetic token and continue
    Insert(TokenKind),
    /// Try to find a synchronization point and continue
    Sync,
}

/// Trait for types that can perform error recovery
pub trait ErrorRecovery {
    /// Attempt to recover from a parse error using the specified strategy
    fn recover(&mut self, error: ParseError, strategy: RecoveryStrategy) -> Result<(), ParseError>;

    /// Check if recovery is possible for the given error and strategy
    fn can_recover(&self, error: &ParseError, strategy: RecoveryStrategy) -> bool;
}

/// Default error recovery implementation
pub struct DefaultErrorRecovery;

impl ErrorRecovery for DefaultErrorRecovery {
    fn recover(&mut self, error: ParseError, strategy: RecoveryStrategy) -> Result<(), ParseError> {
        match strategy {
            RecoveryStrategy::Panic => Err(error),
            RecoveryStrategy::Skip => {
                // Skip strategy - the error is considered handled
                Ok(())
            }
            RecoveryStrategy::Insert(_) => {
                // Insert strategy - synthetic token insertion handled by caller
                Ok(())
            }
            RecoveryStrategy::Sync => {
                // Sync strategy - synchronization handled by caller
                Ok(())
            }
        }
    }

    fn can_recover(&self, _error: &ParseError, strategy: RecoveryStrategy) -> bool {
        match strategy {
            RecoveryStrategy::Panic => false,
            RecoveryStrategy::Skip | RecoveryStrategy::Insert(_) | RecoveryStrategy::Sync => true,
        }
    }
}

/// Context-aware error recovery that tracks recovery attempts
pub struct ContextErrorRecovery {
    recovery_attempts: usize,
    max_recovery_attempts: usize,
}

impl ContextErrorRecovery {
    /// Create a new context-aware error recovery with default limits
    pub fn new() -> Self {
        Self {
            recovery_attempts: 0,
            max_recovery_attempts: 10,
        }
    }

    /// Create with custom maximum recovery attempts
    pub fn with_max_attempts(max_attempts: usize) -> Self {
        Self {
            recovery_attempts: 0,
            max_recovery_attempts: max_attempts,
        }
    }

    /// Reset the recovery attempt counter
    pub fn reset(&mut self) {
        self.recovery_attempts = 0;
    }

    /// Check if we've exceeded the maximum recovery attempts
    pub fn exceeded_limit(&self) -> bool {
        self.recovery_attempts >= self.max_recovery_attempts
    }
}

impl ErrorRecovery for ContextErrorRecovery {
    fn recover(&mut self, error: ParseError, strategy: RecoveryStrategy) -> Result<(), ParseError> {
        if self.exceeded_limit() {
            return Err(error);
        }

        self.recovery_attempts += 1;

        match strategy {
            RecoveryStrategy::Panic => Err(error),
            RecoveryStrategy::Skip => Ok(()),
            RecoveryStrategy::Insert(_) => Ok(()),
            RecoveryStrategy::Sync => Ok(()),
        }
    }

    fn can_recover(&self, _error: &ParseError, strategy: RecoveryStrategy) -> bool {
        if self.exceeded_limit() {
            return false;
        }

        match strategy {
            RecoveryStrategy::Panic => false,
            RecoveryStrategy::Skip | RecoveryStrategy::Insert(_) | RecoveryStrategy::Sync => true,
        }
    }
}

/// Error recovery result indicating what action was taken
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecoveryResult {
    /// Recovery was successful
    Recovered,
    /// Recovery failed, parsing should stop
    Failed,
    /// Recovery inserted synthetic tokens
    Inserted(Vec<TokenKind>),
    /// Recovery skipped tokens
    Skipped(usize),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostic::ParseError;
    use crate::source_manager::SourceSpan;

    #[test]
    fn test_default_recovery_panic() {
        let mut recovery = DefaultErrorRecovery;
        let error = ParseError::SyntaxError {
            message: "test error".to_string(),
            location: SourceSpan::empty(),
        };

        assert!(recovery.recover(error, RecoveryStrategy::Panic).is_err());
        assert!(!recovery.can_recover(&error, RecoveryStrategy::Panic));
    }

    #[test]
    fn test_default_recovery_skip() {
        let mut recovery = DefaultErrorRecovery;
        let error = ParseError::SyntaxError {
            message: "test error".to_string(),
            location: SourceSpan::empty(),
        };

        assert!(recovery.recover(error, RecoveryStrategy::Skip).is_ok());
        assert!(recovery.can_recover(&error, RecoveryStrategy::Skip));
    }

    #[test]
    fn test_context_recovery_limit() {
        let mut recovery = ContextErrorRecovery::with_max_attempts(2);
        let error = ParseError::SyntaxError {
            message: "test error".to_string(),
            location: SourceSpan::empty(),
        };

        // First recovery should succeed
        assert!(recovery.recover(error.clone(), RecoveryStrategy::Skip).is_ok());
        assert!(!recovery.exceeded_limit());

        // Second recovery should succeed
        assert!(recovery.recover(error.clone(), RecoveryStrategy::Skip).is_ok());
        assert!(!recovery.exceeded_limit());

        // Third recovery should fail due to limit
        assert!(recovery.recover(error, RecoveryStrategy::Skip).is_err());
        assert!(recovery.exceeded_limit());
    }
}