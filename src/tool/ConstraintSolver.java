package tool;

import strategy.Outcome;
import strategy.Strategy;
import util.ProcessExec;

import java.io.IOException;
import java.util.concurrent.TimeoutException;

public class ConstraintSolver {

    /**
     * Calls an external solver to solve the given SMT-LIB2 constraint withing the given timeout specificed in
     * milliseconds.
     */
    public ConstraintSolution run(String smtConstraint, Strategy strategy, long timeout)
        throws IOException, InterruptedException, TimeoutException {
        ProcessExec process = new ProcessExec("z3", "-smt2", "-in");

        Outcome outcome;
        long start = System.currentTimeMillis();
        String details = process.execute(smtConstraint, timeout);
        long end = System.currentTimeMillis();
        strategy.decreaseTimeout((end - start));
        if (details.startsWith("sat")) {
            outcome = Outcome.INCORRECT;
        } else if (details.startsWith("unsat")) {
            outcome = Outcome.CORRECT;
        } else {
            System.err.println(details);
            outcome = Outcome.UNKNOWN;
        }
        return new ConstraintSolution(outcome, details);
    }
}
