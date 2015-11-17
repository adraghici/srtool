package tool;

import ast.Program;
import com.google.common.collect.ImmutableList;
import visitor.SMTGenVisitor;

public class SMTGenerator {
    private static final ImmutableList<String> UTILITY_FUNCTIONS = ImmutableList.of(
        "(set-logic QF_BV)",
        "(set-option :produce-models true)",
        "(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))",
        "(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))",
        "(define-fun bvdiv ((x (_ BitVec 32)) (y (_ BitVec 32))) (_ BitVec 32) (ite (not (= y (_ bv0 32))) (bvsdiv x y) x))",
        "(define-fun bvid ((x (_ BitVec 32))) (_ BitVec 32) x)",
        "(define-fun bvtobinary ((x (_ BitVec 32))) (_ BitVec 32) (ite (not (= x (_ bv0 32))) (_ bv0 32) (_ bv1 32)))");
    private static final String CHECK_SAT = "(check-sat)";
    private final Program program;
    private final SMTGenVisitor visitor;

    public SMTGenerator(Program program) {
        this.program = program;
        this.visitor = new SMTGenVisitor();
    }

    public String generateSMT() {
        return String.join("\n", UTILITY_FUNCTIONS)
            + visitor.visit(this.program)
            + CHECK_SAT + "\n"
            + SMTUtil.getValues(visitor.getAssertCount());
    }
}
