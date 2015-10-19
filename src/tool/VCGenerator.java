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

		System.out.println("---------------------");
		System.out.println(smtExpr);
		System.out.println("---------------------");

        return smtExpr;
	}

}
