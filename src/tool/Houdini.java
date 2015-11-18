package tool;

import ast.AssertStmt;
import ast.Node;
import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import visitor.CallVisitor;
import visitor.ReturnVisitor;
import visitor.ShadowingVisitor;
import util.ProgramUtil;
import visitor.Visitor;
import visitor.WhileVisitor;

import java.io.IOException;
import java.util.List;
import java.util.stream.Collectors;

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
            new CallVisitor(candidateAssertCollector),
            new WhileVisitor(candidateAssertCollector),
            new ReturnVisitor(candidateAssertCollector));
    }

    @Override
    public Outcome run() throws IOException, InterruptedException {
        Program dirty = ProgramUtil.transform(program, initialVisitors, states);
        Program clean = ProgramUtil.clean(dirty, states);

        while (true) {
            SMTModel smtModel = generateSMT(clean);
            ConstraintSolution solution = solver.run(smtModel.getCode());

            if (solution.getOutcome() == Outcome.CORRECT) {
                return Outcome.CORRECT;
            } else if (solution.getOutcome() == Outcome.INCORRECT) {
                List<AssertStmt> failed = getFailedAsserts(smtModel, solution);
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

    private SMTModel generateSMT(Program program) {
        SMTGenerator smtGenerator = new SMTGenerator(ProgramUtil.transform(program, iterationVisitors, states));
        return smtGenerator.generateSMT();
    }

    /**
     * Returns the list of asserts failed in the given model.
     */
    private static List<AssertStmt> getFailedAsserts(SMTModel smtModel, ConstraintSolution solution) {
        return SMTUtil.failedAssertionIds(solution.getDetails()).stream()
            .map(smtModel::getAssert)
            .collect(Collectors.toList());
    }

    private boolean nonCandidateAssertionsFailing(List<AssertStmt> failedAsserts) {
        return !candidateAssertCollector.containsAll(failedAsserts);
    }
}
