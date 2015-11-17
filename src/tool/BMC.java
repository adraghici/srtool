package tool;

import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import visitor.CallVisitor;
import visitor.LoopUnwindingVisitor;
import visitor.ReturnVisitor;
import visitor.ShadowingVisitor;
import visitor.Visitor;

import java.io.IOException;
import java.util.List;

public class BMC implements VerificationStrategy {
    private Program program;
    private final ConstraintSolver solver;
    private final List<String> programStates;
    private final ImmutableList<Visitor> TRANSFORMATION_VISITORS = ImmutableList.of(
        new ShadowingVisitor(),
        new CallVisitor(),
        new LoopUnwindingVisitor(),
        new ReturnVisitor());

    public BMC(Program program) {
        this.program = program;
        solver = new ConstraintSolver();
        programStates = Lists.newArrayList();
    }

    @Override
    public String run() throws IOException, InterruptedException {
        TRANSFORMATION_VISITORS.forEach(visitor -> {
            program = (Program) visitor.visit(program);
            programStates.add(program.toString(visitor));
        });

        SMTModel smtModel = new SMTGenerator(program).generateSMT();
        String smtCode = smtModel.getCode();
        programStates.add(smtModel.getCode());

        return solver.run(smtCode).getDecision();
    }

    @Override
    public String toString() {
        return String.join("\n", programStates);
    }
}
