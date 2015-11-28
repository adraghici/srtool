package tool;

import java.util.concurrent.Callable;
import java.util.function.Function;

/**
 * Specification for a verification technique.
 */
public interface Strategy extends Callable<Outcome> {
    public enum Name { CPP, HOUDINI, BMC}

    public Name getName();

    public Function<Outcome, Outcome> getInterpretation();
}
