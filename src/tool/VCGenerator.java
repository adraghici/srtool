package tool;
import parser.SimpleCParser.ProcedureDeclContext;

public class VCGenerator {
	private final ProcedureDeclContext procedure;
	private final SSAVisitor visitor;

	public VCGenerator(ProcedureDeclContext procedure) {
		this.procedure = procedure;
		this.visitor = new SSAVisitor();
	}

	public StringBuilder generateVC() {
		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		result.append("(set-option :produce-models true)\n");
		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");

		// Start the visitor from the single procedure node (for Part I).
		StringBuilder smtProcedure = visitor.visit(this.procedure);
		result.append(smtProcedure);

		result.append("\n(check-sat)\n");
		System.out.println(result);

        return result;
	}
}
