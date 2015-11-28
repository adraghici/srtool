package tool;

import java.util.concurrent.Callable;
import java.util.function.Function;

/**
 * Specification for a verification technique.
 */
public interface Strategy extends Callable<Outcome> {
    public enum Name { CPP, HOUDINI, BMC }


    /**
     * Get the name of the strategy.
     */
    Name getName();

    /**
     * Find out the interpretation of the outcome of the strategy, more exactly whether it returns false
     * posivites, false negatives, or other types of unreliable results.
     */
    Function<Outcome, Outcome> getInterpretation();

    /**
     * Decreased the remaining time for the current strategy by the given number of milliseconds.
     * @param difference
     */
    void decreaseTimeout(long difference);
}
