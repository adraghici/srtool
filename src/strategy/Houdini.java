package strategy;

import ast.AssertStmt;
import ast.Node;
import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import tool.AssertCollector;
import tool.ConstraintSolution;
import tool.ConstraintSolver;
import tool.Outcome;
import tool.SMTModel;
import tool.VerificationStrategy;
import util.ProgramUtil;
import util.StrategyUtil;
import visitor.CallVisitor;
import visitor.ReturnVisitor;
import visitor.ShadowingVisitor;
import visitor.Visitor;
import visitor.WhileVisitor;

import java.io.IOException;
import java.util.List;

public class Houdini implements VerificationStrategy {
    private final Program program;
    private final ConstraintSolver solver;
    private final List<String> states;
    private final AssertCollector candidateAssertCollector;
    private final ImmutableList<Visitor> initialVisitors;
    private final ImmutableList<Visitor> iterationVisitors;

    public Houdini(Program program) {
        this.program = program;
        solver = new ConstraintSolver();
        states = Lists.newArrayList();
        candidateAssertCollector = new AssertCollector();
        initialVisitors = ImmutableList.of(new ShadowingVisitor());
        iterationVisitors = ImmutableList.of(
            CallVisitor.withCandidates(candidateAssertCollector),
            new WhileVisitor(candidateAssertCollector),
            ReturnVisitor.withCandidates(candidateAssertCollector));
    }

    @Override
    public Outcome call() throws IOException, InterruptedException {
        Program dirty = ProgramUtil.transform(program, initialVisitors, states);
        Program clean = ProgramUtil.clean(dirty, states);

        while (true) {
            if (Thread.currentThread().isInterrupted()) {
                return Outcome.UNKNOWN;
            }

            SMTModel smtModel = StrategyUtil.generateSMT(clean, iterationVisitors, states);
            ConstraintSolution solution = solver.run(smtModel.getCode());

            if (solution.getOutcome() == Outcome.CORRECT) {
                return Outcome.CORRECT;
            } else if (solution.getOutcome() == Outcome.INCORRECT) {
                List<AssertStmt> failed = StrategyUtil.getFailedAsserts(smtModel, solution);
                if (nonCandidateAssertionsFailing(failed)) {
                    return Outcome.INCORRECT;
                }

                List<Node> failedCandidates = candidateAssertCollector.resolve(failed);
                clean = ProgramUtil.prune(clean, failedCandidates, states);
                candidateAssertCollector.clear();
            }
        }
    }

    @Override
    public String toString() {
        return String.join("\n", states);
    }

    private boolean nonCandidateAssertionsFailing(List<AssertStmt> failedAsserts) {
        return !candidateAssertCollector.containsAll(failedAsserts);
    }
}
