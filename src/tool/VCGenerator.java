package tool;
import parser.SimpleCParser.ProcedureDeclContext;

public class VCGenerator {

	private ProcedureDeclContext proc;
	private VCGeneratorVisitor visitor;

	public VCGenerator(ProcedureDeclContext proc) {
		this.proc = proc;
		this.visitor = new VCGeneratorVisitor();
	}

	public StringBuilder generateVC() {
		// Start the visitor from the single procedure node (for Part I).
		StringBuilder smtExpr = visitor.visit(this.proc);

		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		result.append("(set-option :produce-models true)\n");
		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");

		result.append("\n(check-sat)\n");

        return result;
	}

}
