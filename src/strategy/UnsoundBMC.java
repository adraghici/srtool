package strategy;

import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
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

public class UnsoundBMC implements Strategy {
    private final Program program;
    private final ConstraintSolver solver;
    private final List<String> states;

    public UnsoundBMC(Program program) {
        this.program = program;
        solver = new ConstraintSolver();
        states = Lists.newArrayList();
    }

    @Override
    public Outcome call() throws IOException, InterruptedException {
        for (int depth = StrategyUtil.BMC_START_DEPTH; ; depth += StrategyUtil.BMC_STEP) {
            if (Thread.currentThread().isInterrupted()) {
                return Outcome.UNKNOWN;
            }

            SMTModel smtModel = StrategyUtil.generateSMT(program, createVisitorsWithDepth(depth), states);
            ConstraintSolution solution = solver.run(smtModel.getCode());

            if (solution.getOutcome() == Outcome.INCORRECT) {
                return Outcome.INCORRECT;
            }
        }
    }

    @Override
    public Name getName() {
        return Name.UNSOUND_BMC;
    }

    @Override
    public String toString() {
        return String.join("\n", states);
    }

    private ImmutableList<Visitor> createVisitorsWithDepth(int depth) {
        AssertCollector assertCollector = new AssertCollector();
        return ImmutableList.of(
            new CallVisitor(assertCollector),
            UnwindingVisitor.createUnsound(depth),
            new ShadowingVisitor(assertCollector),
            new ReturnVisitor(assertCollector));
    }
}
