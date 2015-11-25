package strategy;

import ast.Node;
import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import tool.AssertCollector;
import tool.ConstraintSolution;
import tool.ConstraintSolver;
import tool.Outcome;
import tool.SMTModel;
import tool.Strategy;
import util.StrategyUtil;
import visitor.CallVisitor;
import visitor.ReturnVisitor;
import visitor.ShadowingVisitor;
import visitor.UnwindingVisitor;
import visitor.Visitor;

import java.io.IOException;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

/**
 * Sound BMC is always reliable as long as it finishes executing, as reflected in the interpretation.
 */
public class SoundBMC implements Strategy {
    private final Program program;
    private final ConstraintSolver solver;
    private final List<String> states;
    private final AssertCollector assertCollector;
    private final Set<Node> unwindingAsserts;

    public SoundBMC(Program program) {
        this.program = program;
        solver = new ConstraintSolver();
        states = Lists.newArrayList();
        assertCollector = new AssertCollector();
        unwindingAsserts = Sets.newHashSet();
    }

    @Override
    public Outcome call() throws IOException, InterruptedException {
        for (int depth = StrategyUtil.BMC_START_DEPTH; ; depth += StrategyUtil.BMC_STEP) {
            if (Thread.currentThread().isInterrupted()) {
                return Outcome.UNKNOWN;
            }

            SMTModel smtModel = StrategyUtil.generateSMT(program, createVisitorsWithDepth(depth), states);
            ConstraintSolution solution = solver.run(smtModel.getCode());

            if (solution.getOutcome() == Outcome.CORRECT) {
                return Outcome.CORRECT;
            }

            List<Node> failedAsserts = assertCollector.resolve(StrategyUtil.getFailedAsserts(smtModel, solution));
            if (originalAssertsFailing(failedAsserts)) {
                return Outcome.INCORRECT;
            }

            assertCollector.clear();
        }
    }

    @Override
    public Name getName() {
        return Name.SOUND_BMC;
    }

    @Override
    public Function<Outcome, Outcome> getInterpretation() {
        return Function.identity();
    }

    @Override
    public String toString() {
        return String.join("\n", states);
    }

    private boolean originalAssertsFailing(List<Node> failedAsserts) {
        return failedAsserts.isEmpty() || !failedAsserts.stream().allMatch(unwindingAsserts::contains);
    }

    private ImmutableList<Visitor> createVisitorsWithDepth(int depth) {
        return ImmutableList.of(
            new CallVisitor(assertCollector),
            UnwindingVisitor.createSound(assertCollector, unwindingAsserts, depth),
            new ShadowingVisitor(assertCollector),
            new ReturnVisitor(assertCollector));
    }
}
