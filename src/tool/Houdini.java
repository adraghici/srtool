package tool;

import ast.AssertStmt;
import ast.Node;
import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import visitor.CallVisitor;
import visitor.DefaultVisitor;
import visitor.RemovingVisitor;
import visitor.ReturnVisitor;
import visitor.ShadowingVisitor;
import visitor.Visitor;
import visitor.WhileVisitor;

import java.io.IOException;
import java.util.List;
import java.util.stream.Collectors;

public class Houdini implements VerificationStrategy {
    private Program program;
    private final ConstraintSolver solver;
    private final List<String> programStates;
    private final AssertCollector assertCollector;
    private final ImmutableList<Visitor> mutatingVisitors;

    public Houdini(Program program) {
        this.program = program;
        solver = new ConstraintSolver();
        programStates = Lists.newArrayList();
        assertCollector = new AssertCollector();
        mutatingVisitors = ImmutableList.of(
            new CallVisitor(assertCollector),
            new WhileVisitor(assertCollector),
            new ReturnVisitor(assertCollector));
    }

    @Override
    public String run() throws IOException, InterruptedException {

        // Apply the Shadowing Visitor.
        program = applyVisitor(new ShadowingVisitor(), program);

        // Make a new (deep) copy of the Program.
        Program oldProgram = (Program) new DefaultVisitor().visit(program);

        while (true) {
            // Apply Call, While and Return Visitors.
            mutatingVisitors.forEach(visitor -> program = applyVisitor(visitor, program));

            SMTModel smtModel = new SMTGenerator(program).generateSMT();
            String smtCode = smtModel.getCode();
            programStates.add(smtCode);

            ConstraintSolution solution = solver.run(smtCode);
            String decision = solution.getDecision();

            if (decision.equals("CORRECT")) {
                return "CORRECT";
            } else if (decision.equals("INCORRECT")) {
                // Find whether we have failing assertions on candidate pre/post/invariants.
                List<AssertStmt> assertStmts =
                    SMTUtil.failedAssertionIds(solution.getDetails()).stream()
                        .map(id -> smtModel.getIndexToAssert().get(id))
                        .collect(Collectors.toList());

                List<Node> nodes = assertCollector.resolve(assertStmts);
                if (nodes.isEmpty()) {
                    return "INCORRECT";
                }

                // Remove nodes from oldProgram.
                program = (Program) oldProgram.accept(new RemovingVisitor(nodes));
            }

            assertCollector.clear();
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
