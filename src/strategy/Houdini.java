package strategy;

import ast.Node;
import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import tool.ConstraintSolution;
import tool.ConstraintSolver;
import tool.NodeCollector;
import tool.SMTModel;
import util.ProgramUtil;
import util.StrategyUtil;
import visitor.CallVisitor;
import visitor.CandidateVisitor;
import visitor.InvariantGenVisitor;
import visitor.ReturnVisitor;
import visitor.ShadowingVisitor;
import visitor.Visitor;
import visitor.WhileVisitor;

import java.io.IOException;
import java.util.List;
import java.util.Set;
import java.util.concurrent.TimeoutException;
import java.util.function.Function;

/**
 * Houdini may return false negatives, as reflected in the interpretation.
 */
public class Houdini implements Strategy {
    private final Program program;
    private long timeout;
    private final boolean inferInvariants;
    private final ConstraintSolver solver;
    private final List<String> states;
    private final NodeCollector nodeCollector;
    private final Set<Node> artificialConditions;
    private final List<Visitor> initialVisitors;
    private final List<Visitor> iterationVisitors;

    public static Houdini withInvariantInference(Program program, long timeout) {
        return new Houdini(program, timeout, true);
    }

    public static Houdini basic(Program program, long timeout) {
        return new Houdini(program, timeout, false);
    }

    public Houdini(Program program, long timeout, boolean inferInvariants) {
        this.program = program;
        this.timeout = timeout;
        this.inferInvariants = inferInvariants;
        solver = new ConstraintSolver();
        states = Lists.newArrayList();
        nodeCollector = new NodeCollector();
        artificialConditions = Sets.newHashSet();
        initialVisitors = createInitialVisitors();
        iterationVisitors = createIterationVisitors();
    }

    @Override
    public Outcome call() throws IOException, InterruptedException, TimeoutException {
        Program clean = ProgramUtil.transform(program, initialVisitors, states);

        while (true) {
            if (Thread.currentThread().isInterrupted()) {
                return Outcome.UNKNOWN;
            }

            SMTModel smtModel = StrategyUtil.generateSMT(clean, iterationVisitors, states);
            ConstraintSolution solution = solver.run(smtModel.getCode(), this, timeout);

            if (solution.getOutcome() == Outcome.CORRECT) {
                return Outcome.CORRECT;
            } else if (solution.getOutcome() == Outcome.INCORRECT) {
                List<Node> failedConditions = nodeCollector.resolve(StrategyUtil.getFailedAsserts(smtModel, solution));

                if (nonCandidateConditionsFailing(failedConditions)) {
                    return Outcome.INCORRECT;
                }

                nodeCollector.clear();
                clean = ProgramUtil.prune(clean, failedConditions, artificialConditions, nodeCollector, states);
            } else {
                return Outcome.UNKNOWN;
            }
        }
    }

    @Override
    public Name getName() {
        return Name.HOUDINI;
    }

    @Override
    public Function<Outcome, Outcome> getInterpretation() {
        return outcome -> outcome == Outcome.CORRECT ? outcome : Outcome.UNKNOWN;
    }

    @Override
    public void decreaseTimeout(long difference) {
        timeout -= difference;
    }

    @Override
    public String toString() {
        return String.join("\n", states);
    }

    private boolean nonCandidateConditionsFailing(List<Node> failedConditions) {
        return failedConditions.isEmpty() || !failedConditions.stream().allMatch(artificialConditions::contains);
    }

    private ImmutableList<Visitor> createInitialVisitors() {
        List<Visitor> visitors = Lists.newArrayList();
        if (inferInvariants) {
            visitors.add(new InvariantGenVisitor());
        }
        visitors.add(new ShadowingVisitor(nodeCollector));
        visitors.add(new CandidateVisitor(nodeCollector, artificialConditions));
        return ImmutableList.copyOf(visitors);
    }

    private ImmutableList<Visitor> createIterationVisitors() {
        return ImmutableList.of(
            new CallVisitor(nodeCollector),
            new WhileVisitor(nodeCollector),
            new ReturnVisitor(nodeCollector));
    }
}
