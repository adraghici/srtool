package tool;

import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import util.ProgramUtil;
import visitor.CallVisitor;
import visitor.UnwindingVisitor;
import visitor.ReturnVisitor;
import visitor.ShadowingVisitor;
import visitor.Visitor;

import java.io.IOException;
import java.util.List;

public class BMC implements VerificationStrategy {
    private final Program program;
    private final ConstraintSolver solver;
    private final List<String> states;
    private final AssertCollector assertCollector;

    public BMC(Program program) {
        this.program = program;
        solver = new ConstraintSolver();
        states = Lists.newArrayList();
        assertCollector = new AssertCollector();
    }

    @Override
    public Outcome run() throws IOException, InterruptedException {
        String smtCode = generateSMT(program, 4);
        return solver.run(smtCode).getOutcome();
    }

    @Override
    public String toString() {
        return String.join("\n", states);
    }

    private String generateSMT(Program program, int depth) {
        Program transformed = ProgramUtil.transform(program, createVisitorsWithDepth(depth), states);
        SMTGenerator smtGenerator = new SMTGenerator(transformed);
        return smtGenerator.generateSMT().getCode();
    }

    private ImmutableList<Visitor> createVisitorsWithDepth(int depth) {
        return ImmutableList.of(
            new CallVisitor(assertCollector),
            new UnwindingVisitor(depth),
            new ShadowingVisitor(),
            new ReturnVisitor(assertCollector));
    }
}
