package tool;

import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import visitor.CallVisitor;
import visitor.LoopUnwindingVisitor;
import visitor.ReturnVisitor;
import visitor.ShadowingVisitor;
import visitor.Visitor;

import java.util.List;

public class BMC implements VerificationStrategy {
    private Program program;
    private final List<String> programStates;
    private final ImmutableList<Visitor> TRANSFORMATION_VISITORS = ImmutableList.of(
        new ShadowingVisitor(),
        new CallVisitor(),
        new LoopUnwindingVisitor(),
        new ReturnVisitor());

    public BMC(Program program) {
        this.program = program;
        programStates = Lists.newArrayList();
    }

    @Override
    public SMTModel run() {
        TRANSFORMATION_VISITORS.forEach(visitor -> {
            program = (Program) visitor.visit(program);
            programStates.add(program.toString(visitor));
        });

        SMTModel smtModel = new SMTGenerator(program).generateSMT();
        programStates.add(smtModel.getCode());

        return smtModel;
    }

    @Override
    public String toString() {
        return String.join("\n", programStates);
    }
}
