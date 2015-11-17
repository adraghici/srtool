package tool;

import util.ProcessExec;
import util.ProcessTimeoutException;

import java.io.IOException;

public class ConstraintSolver {
    private static final int TIMEOUT = 30000;

    public ConstraintSolution run(String smtConstraint) throws IOException, InterruptedException {
        ProcessExec process = new ProcessExec("z3", "-smt2", "-in");
        String details = "";
        String decision = "";
        try {
            details = process.execute(smtConstraint, TIMEOUT);
            if (details.startsWith("sat")) {
                decision = "INCORRECT";
            } else if (details.startsWith("unsat")) {
                decision = "CORRECT";
            } else {
                decision = "UNKNOWN";
            }
        } catch (ProcessTimeoutException e) {
            decision = "UNKNOWN";
        } finally {
            return new ConstraintSolution(decision, details);
        }
    }
}
