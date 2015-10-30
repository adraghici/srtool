package tool;

import parser.SimpleCParser.ProgramContext;

public class VCGenerator {
    private final ProgramContext program;
    private final SSAVisitor visitor;

    public VCGenerator(ProgramContext program) {
        this.program = program;
        this.visitor = new SSAVisitor();
    }

    public StringBuilder generateVC() {
        StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
        // result.append("(set-option :pp.bv-literals false)");
        result.append("(set-option :produce-models true)\n");
        result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
        result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");
        result.append("(define-fun bvdiv ((x (_ BitVec 32)) (y (_ BitVec 32))) (_ BitVec 32) (ite (not (= y (_ bv0 32))) (bvsdiv x y) x))\n");
        result.append("(define-fun bvid ((x (_ BitVec 32))) (_ BitVec 32) x)\n");
        result.append("(define-fun bvtobinary ((x (_ BitVec 32))) (_ BitVec 32) (ite (not (= x (_ bv0 32))) (_ bv0 32) (_ bv1 32)))\n");

        // Start the visitor from the single program node (for Part I).
        String smtProcedure = visitor.visit(this.program);
        result.append(smtProcedure);

        result.append("\n(check-sat)\n");
        System.out.println(result);
        // result.append("(get-model)");

        return result;
    }
}
