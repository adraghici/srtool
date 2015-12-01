package tool;

import strategy.Outcome;

public class ConstraintSolution {
    private final Outcome outcome;
    private final String details;

    public ConstraintSolution(Outcome outcome, String details) {
        this.outcome = outcome;
        this.details = details;
    }

    public Outcome getOutcome() {
        return outcome;
    }

    public String getDetails() {
        return details;
    }
}
