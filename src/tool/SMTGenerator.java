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

    public String generateSMT() {
        return SMTUtil.predefinedFunctions()
            + visitor.visit(this.program)
            + SMTUtil.checkSAT()
            + SMTUtil.getValues(visitor.getAssertCount());
    }
}
