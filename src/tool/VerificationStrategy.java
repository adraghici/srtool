package tool;

import java.util.concurrent.Callable;

/**
 * Specification for a verification technique.
 */
public interface VerificationStrategy extends Callable<Outcome> {
}
