package tool;

public class ConstraintSolution {
    private final String decision;
    private final String details;

    public ConstraintSolution(String decision, String details) {
        this.decision = decision;
        this.details = details;
    }

    public String getDetails() {
        return details;
    }

    public String getDecision() {
        return decision;
    }
}
