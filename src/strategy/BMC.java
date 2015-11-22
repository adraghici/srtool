package strategy;

import ast.AssertStmt;
import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import tool.AssertCollector;
import tool.ConstraintSolution;
import tool.ConstraintSolver;
import tool.Outcome;
import tool.SMTModel;
import tool.VerificationStrategy;
import util.StrategyUtil;
import visitor.CallVisitor;
import visitor.ReturnVisitor;
import visitor.ShadowingVisitor;
import visitor.UnwindingVisitor;
import visitor.Visitor;

import java.io.IOException;
import java.util.List;

public class BMC implements VerificationStrategy {
    private static final int MIN_DEPTH = 5;
    private static final int MAX_DEPTH = 100;
    private static final int DEPTH_STEP = 3;
    private final Program program;
    private final ConstraintSolver solver;
    private final List<String> states;
    private final AssertCollector unwindingAssertCollector;

    public BMC(Program program) {
        this.program = program;
        solver = new ConstraintSolver();
        states = Lists.newArrayList();
        unwindingAssertCollector = new AssertCollector();
    }

    @Override
    public Outcome call() throws IOException, InterruptedException {
        for (int depth = MIN_DEPTH; depth <= MAX_DEPTH; depth += DEPTH_STEP) {
            if (Thread.currentThread().isInterrupted()) {
                return Outcome.UNKNOWN;
            }

            SMTModel smtModel = StrategyUtil.generateSMT(program, createVisitorsWithDepth(depth), states);
            ConstraintSolution solution = solver.run(smtModel.getCode());

            if (solution.getOutcome() == Outcome.CORRECT) {
                return Outcome.CORRECT;
            }

            List<AssertStmt> failed = StrategyUtil.getFailedAsserts(smtModel, solution);
            if (!unwindingAssertionFailing(failed)) {
                return Outcome.INCORRECT;
            }
        }
        return Outcome.UNKNOWN;
    }

    @Override
    public String toString() {
        return String.join("\n", states);
    }

    private boolean unwindingAssertionFailing(List<AssertStmt> failedAsserts) {
        return unwindingAssertCollector.containsAny(failedAsserts);
    }

    private ImmutableList<Visitor> createVisitorsWithDepth(int depth) {
        return ImmutableList.of(
            CallVisitor.withoutCandidates(unwindingAssertCollector),
            new UnwindingVisitor(unwindingAssertCollector, depth),
            new ShadowingVisitor(),
            ReturnVisitor.withoutCandidates(unwindingAssertCollector));
    }
}
