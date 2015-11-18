package tool;

import ast.AssertStmt;
import ast.Node;
import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import visitor.CallVisitor;
import visitor.RemovingVisitor;
import visitor.ReturnVisitor;
import visitor.ShadowingVisitor;
import visitor.Visitor;
import visitor.WhileVisitor;

import java.io.IOException;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

public class Houdini implements VerificationStrategy {
    private Program program;
    private final ConstraintSolver solver;
    private final List<String> programStates;
    private final CandidateAssertCollector candidateAssertCollector;
    private final ImmutableList<Visitor> mutatingVisitors;

    public Houdini(Program program) {
        this.program = program;
        solver = new ConstraintSolver();
        programStates = Lists.newArrayList();
        candidateAssertCollector = new CandidateAssertCollector();
        mutatingVisitors = ImmutableList.of(
            new CallVisitor(candidateAssertCollector),
            new WhileVisitor(candidateAssertCollector),
            new ReturnVisitor(candidateAssertCollector));
    }

    @Override
    public String run() throws IOException, InterruptedException {
        // Apply the Shadowing Visitor.
        program = applyVisitor(new ShadowingVisitor(), program);

        // Make a new (deep) copy of the Program.
        Program cleanProgram = (Program) new RemovingVisitor(Collections.emptyList()).visit(program);

        while (true) {
            // Apply Call, While and Return Visitors.
            Program currentProgram = cleanProgram;
            for (Visitor visitor : mutatingVisitors) {
                currentProgram = applyVisitor(visitor, currentProgram);
            }

            SMTModel smtModel = new SMTGenerator(currentProgram).generateSMT();
            String smtCode = smtModel.getCode();
            programStates.add(smtCode);

            ConstraintSolution solution = solver.run(smtCode);
            String decision = solution.getDecision();

            if (decision.equals("CORRECT")) {
                return "CORRECT";
            } else if (decision.equals("INCORRECT")) {
                // Find whether we have failing assertions on candidate pre/post/invariants.
                List<AssertStmt> failedAsserts =
                    SMTUtil.failedAssertionIds(solution.getDetails()).stream()
                        .map(id -> smtModel.getIndexToAssert().get(id))
                        .collect(Collectors.toList());

                List<Node> failedAssertsSources = candidateAssertCollector.resolve(failedAsserts);
                if (!candidateAssertCollector.filterNonCandidate(failedAsserts).isEmpty()) {
                    return "INCORRECT";
                }

                // Remove failedAssertsSources from cleanProgram.
                cleanProgram = applyVisitor(new RemovingVisitor(failedAssertsSources), cleanProgram);
            }

            candidateAssertCollector.clear();
        }
    }

    private Program applyVisitor(Visitor visitor, Program program) {
        Program resultedProgram = (Program) visitor.visit(program);
        programStates.add(resultedProgram.toString(visitor));
        return resultedProgram;
    }

    @Override
    public String toString() {
        return String.join("\n", programStates);
    }
}
