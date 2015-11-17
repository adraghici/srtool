package tool;

import java.io.IOException;

/**
 * Specification for a verification technique.
 */
public interface VerificationStrategy {
    String run() throws IOException, InterruptedException;
}
