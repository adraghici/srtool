package tool;

import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import util.ProgramUtil;
import visitor.CallVisitor;
import visitor.LoopUnwindingVisitor;
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
    private final ImmutableList<Visitor> visitors;

    public BMC(Program program) {
        this.program = program;
        solver = new ConstraintSolver();
        states = Lists.newArrayList();
        assertCollector = new AssertCollector();
        visitors = ImmutableList.of(
            new ShadowingVisitor(),
            new CallVisitor(assertCollector),
            new LoopUnwindingVisitor(),
            new ReturnVisitor(assertCollector));
    }

    @Override
    public Outcome run() throws IOException, InterruptedException {
        String smtCode = generateSMT(program);
        return solver.run(smtCode).getOutcome();
    }

    @Override
    public String toString() {
        return String.join("\n", states);
    }

    private String generateSMT(Program program) {
        SMTGenerator smtGenerator = new SMTGenerator(ProgramUtil.transform(program, visitors, states));
        return smtGenerator.generateSMT().getCode();
    }
}
