package tool;

import java.util.concurrent.Callable;

/**
 * Specification for a verification technique.
 */
public interface Strategy extends Callable<Outcome> {
    public enum Name { HOUDINI, SOUND_BMC, UNSOUND_BMC }

    public Name getName();
}
