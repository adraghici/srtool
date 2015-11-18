package tool;

import java.io.IOException;

/**
 * Specification for a verification technique.
 */
public interface VerificationStrategy {
    Outcome run() throws IOException, InterruptedException;
}
