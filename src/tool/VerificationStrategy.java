package tool;

/**
 * Specification for a verification technique.
 */
public interface VerificationStrategy {
    SMTModel run();
}
