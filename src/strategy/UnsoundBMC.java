package strategy;

import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import tool.AssertCollector;
import tool.ConstraintSolver;
import tool.Outcome;
import tool.SMTGenerator;
import tool.VerificationStrategy;
import util.ProgramUtil;
import visitor.CallVisitor;
import visitor.ReturnVisitor;
import visitor.ShadowingVisitor;
import visitor.UnwindingVisitor;
import visitor.Visitor;

import java.io.IOException;
import java.util.List;

public class UnsoundBMC implements VerificationStrategy {
    private static final int MIN_DEPTH = 1;
    private static final int MAX_DEPTH = 100;
    private static final int DEPTH_STEP = 2;
    private final Program program;
    private final ConstraintSolver solver;
    private final List<String> states;
    private final AssertCollector assertCollector;

    public UnsoundBMC(Program program) {
        this.program = program;
        solver = new ConstraintSolver();
        states = Lists.newArrayList();
        assertCollector = new AssertCollector();
    }

    @Override
    public Outcome run() throws IOException, InterruptedException {
        Outcome outcome = Outcome.CORRECT;
        for (int depth = MIN_DEPTH; depth < MAX_DEPTH && outcome == Outcome.CORRECT; depth += DEPTH_STEP) {
            String smtCode = generateSMT(program, depth);
            outcome = solver.run(smtCode).getOutcome();
        }
        return outcome;
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
