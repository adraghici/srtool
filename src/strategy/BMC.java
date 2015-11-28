package strategy;

import ast.Node;
import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import tool.ConstraintSolution;
import tool.ConstraintSolver;
import tool.NodeCollector;
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
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeoutException;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Sound BMC is always reliable as long as it finishes executing, while unsound BMC may return false positives.
 */
public class BMC implements Strategy {
    public static final int INITIAL_DEPTH = 1;
    public static final int DEPTH_STEP = 3;

    private final Program program;
    private long timeout;
    private final ConstraintSolver solver;
    private final List<String> states;
    private final NodeCollector nodeCollector;
    private final Set<Node> unwindingAsserts;
    private final Map<Node, Integer> unwindingDepths;
    private final Map<Node, Node> assertLocations;

    public BMC(Program program, long timeout) {
        this.program = program;
        this.timeout = timeout;
        solver = new ConstraintSolver();
        states = Lists.newArrayList();
        nodeCollector = new NodeCollector();
        unwindingAsserts = Sets.newHashSet();
        unwindingDepths = Maps.newHashMap();
        assertLocations = Maps.newHashMap();
    }

    @Override
    public Outcome call() throws IOException, InterruptedException, TimeoutException {
        List<Node> failedLoops = Lists.newArrayList();

        while (true) {
            if (Thread.currentThread().isInterrupted()) {
                return Outcome.UNKNOWN;
            }

            adjustUnwindingDepths(failedLoops);

            // Unsound BMC.
            SMTModel smtModel = StrategyUtil.generateSMT(program, createUnsoundVisitors(), states);
            ConstraintSolution solution = solver.run(smtModel.getCode(), this, timeout);
            if (solution.getOutcome() == Outcome.INCORRECT) {
                return Outcome.INCORRECT;
            }
            nodeCollector.clear();

            // Sound BMC.
            smtModel = StrategyUtil.generateSMT(program, createSoundVisitors(), states);
            solution = solver.run(smtModel.getCode(), this, timeout);
            if (solution.getOutcome() == Outcome.CORRECT) {
                return Outcome.CORRECT;
            }

            List<Node> failedAsserts = nodeCollector.resolve(StrategyUtil.getFailedAsserts(smtModel, solution));
            if (originalAssertsFailing(failedAsserts)) {
                return Outcome.INCORRECT;
            }

            failedLoops = resolve(failedAsserts);

            nodeCollector.clear();
        }
    }

    @Override
    public Name getName() {
        return Name.BMC;
    }

    @Override
    public Function<Outcome, Outcome> getInterpretation() {
        return Function.identity();
    }

    @Override
    public void decreaseTimeout(long difference) {
        timeout -= difference;
    }

    @Override
    public String toString() {
        return String.join("\n", states);
    }

    private List<Node> resolve(List<Node> failedAsserts) {
        return failedAsserts.stream()
            .filter(assertLocations::containsKey)
            .map(assertLocations::get)
            .collect(Collectors.toList());
    }

    private boolean originalAssertsFailing(List<Node> failedAsserts) {
        return failedAsserts.isEmpty() || !failedAsserts.stream().allMatch(unwindingAsserts::contains);
    }

    private void adjustUnwindingDepths(List<Node> failedLoops) {
        failedLoops.forEach(loop -> {
            if (!unwindingDepths.containsKey(loop)) {
                unwindingDepths.put(loop, INITIAL_DEPTH);
            } else {
                unwindingDepths.put(loop, unwindingDepths.get(loop) + DEPTH_STEP);
            }
        });
    }

    private List<Visitor> createSoundVisitors() {
        return createVisitors(true);
    }

    private List<Visitor> createUnsoundVisitors() {
        return createVisitors(false);
    }

    private List<Visitor> createVisitors(boolean sound) {
        return ImmutableList.of(
            new CallVisitor(nodeCollector),
            new UnwindingVisitor(nodeCollector, unwindingDepths, unwindingAsserts, assertLocations, sound),
            new ShadowingVisitor(nodeCollector),
            new ReturnVisitor(nodeCollector));
    }
}
