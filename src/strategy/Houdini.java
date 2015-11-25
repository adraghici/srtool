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
import util.ProgramUtil;
import util.StrategyUtil;
import visitor.CallVisitor;
import visitor.CandidateVisitor;
import visitor.ReturnVisitor;
import visitor.ShadowingVisitor;
import visitor.Visitor;
import visitor.WhileVisitor;

import java.io.IOException;
import java.util.List;
import java.util.Set;

public class Houdini implements Strategy {
    private final Program program;
    private final ConstraintSolver solver;
    private final List<String> states;
    private final AssertCollector assertCollector;
    private final Set<Node> artificialConditions;
    private final ImmutableList<Visitor> initialVisitors;
    private final ImmutableList<Visitor> iterationVisitors;

    public Houdini(Program program) {
        this.program = program;
        solver = new ConstraintSolver();
        states = Lists.newArrayList();
        assertCollector = new AssertCollector();
        artificialConditions = Sets.newHashSet();
        initialVisitors = ImmutableList.of(
            new ShadowingVisitor(assertCollector),
            new CandidateVisitor(assertCollector, artificialConditions));
        iterationVisitors = ImmutableList.of(
            new CallVisitor(assertCollector),
            new WhileVisitor(assertCollector),
            new ReturnVisitor(assertCollector));
    }

    @Override
    public Outcome call() throws IOException, InterruptedException {
        Program clean = ProgramUtil.transform(program, initialVisitors, states);

        while (true) {
            if (Thread.currentThread().isInterrupted()) {
                return Outcome.UNKNOWN;
            }

            SMTModel smtModel = StrategyUtil.generateSMT(clean, iterationVisitors, states);
            ConstraintSolution solution = solver.run(smtModel.getCode());

            if (solution.getOutcome() == Outcome.CORRECT) {
                return Outcome.CORRECT;
            } else if (solution.getOutcome() == Outcome.INCORRECT) {
                List<Node> failedConditions = assertCollector.resolve(StrategyUtil.getFailedAsserts(smtModel, solution));

                if (nonCandidateConditionsFailing(failedConditions)) {
                    return Outcome.INCORRECT;
                }

                assertCollector.clear();
                clean = ProgramUtil.prune(clean, failedConditions, artificialConditions, assertCollector, states);
            }
        }
    }

    @Override
    public Name getName() {
        return Name.HOUDINI;
    }

    @Override
    public String toString() {
        return String.join("\n", states);
    }

    private boolean nonCandidateConditionsFailing(List<Node> failedConditions) {
        return failedConditions.isEmpty() || !failedConditions.stream().allMatch(artificialConditions::contains);
    }
}
