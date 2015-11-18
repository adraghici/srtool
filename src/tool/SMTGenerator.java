package tool;

import ast.Program;
import visitor.SMTGenVisitor;

public class SMTGenerator {
    private final Program program;
    private final SMTGenVisitor visitor;

    public SMTGenerator(Program program) {
        this.program = program;
        this.visitor = new SMTGenVisitor();
    }

    public SMTModel generateSMT() {
        return new SMTModel(
            visitor.getIndexToAssert(),
            SMTUtil.predefinedFunctions()
                + visitor.visit(program)
                + SMTUtil.checkSAT()
                + SMTUtil.getValues(visitor.getAssertCount()));
    }
}
