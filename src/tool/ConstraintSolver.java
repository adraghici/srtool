package tool;

import util.ProcessExec;
import util.ProcessTimeoutException;

import java.io.IOException;

public class ConstraintSolver {
    private static final int TIMEOUT = 30000;

    public ConstraintSolution run(String smtConstraint) throws IOException, InterruptedException {
        ProcessExec process = new ProcessExec("z3", "-smt2", "-in");
        String details = "";
        Outcome outcome = Outcome.UNKNOWN;
        try {
            details = process.execute(smtConstraint, TIMEOUT);
            if (details.startsWith("sat")) {
                outcome = Outcome.INCORRECT;
            } else if (details.startsWith("unsat")) {
                outcome = Outcome.CORRECT;
            } else {
                outcome = Outcome.UNKNOWN;
            }
        } catch (ProcessTimeoutException e) {
            outcome = Outcome.UNKNOWN;
        } finally {
            return new ConstraintSolution(outcome, details);
        }
    }
}
