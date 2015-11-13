package tool;

import ast.ASTBuilder;
import ast.Program;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import parser.SimpleCLexer;
import parser.SimpleCParser;
import parser.SimpleCParser.ProgramContext;
import util.ProcessExec;
import util.ProcessTimeoutException;
import visitor.ShadowingVisitor;
import visitor.WhileVisitor;

import java.io.FileInputStream;
import java.io.IOException;

public class SRTool {

    private static final int TIMEOUT = 30000;

    public static void main(String[] args) throws IOException, InterruptedException {
        // First pass to create the shadow variables.
        String filename = args[0];
        ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filename));
        ProgramContext ctx = getProgramContext(input, filename);
        Program program = ASTBuilder.build((ProgramContext) ctx.getChild(0).getParent());
        ShadowingVisitor shadowingVisitor = new ShadowingVisitor();
        String content = shadowingVisitor.visit(program);
        // System.out.println(content);

        // Second pass to perform the SSA conversion.
        input = new ANTLRInputStream(content);
        ctx = getProgramContext(input, filename);
        program = ASTBuilder.build((ProgramContext) ctx.getChild(0).getParent());

        // Run the WhileVisitor.
        WhileVisitor whileVisitor = new WhileVisitor();
        program = (Program) whileVisitor.visit(program);

        VCGenerator vcGenerator = new VCGenerator(program);
        String vc = vcGenerator.generateVC().toString();

        String dir = System.getProperty("user.dir");
        String tool = "srtool";
        dir = dir.substring(0, dir.lastIndexOf(tool) + tool.length());
        ProcessExec process = new ProcessExec(dir + "/z3", "-smt2", "-in");
        String queryResult = "";
        try {
            queryResult = process.execute(vc, TIMEOUT);
            // System.out.println(queryResult);
        } catch (ProcessTimeoutException e) {
            System.out.println("UNKNOWN");
            System.exit(1);
        }

        if (queryResult.startsWith("sat")) {
            System.out.println("INCORRECT");
            System.exit(0);
        }

        if (!queryResult.startsWith("unsat")) {
            System.out.println("UNKNOWN");
            System.out.println(queryResult);
            System.exit(1);
        }

        System.out.println("CORRECT");
        System.exit(0);

    }

    private static ProgramContext getProgramContext(ANTLRInputStream input, String filename) {
        SimpleCLexer lexer = new SimpleCLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        SimpleCParser parser = new SimpleCParser(tokens);
        ProgramContext ctx = parser.program();

        if(parser.getNumberOfSyntaxErrors() > 0) {
            System.exit(1);
        }

        Typechecker tc = new Typechecker();
        tc.visit(ctx);
        tc.resolve();

        if(tc.hasErrors()) {
            System.err.println("Errors were detected when typechecking " + filename + ":");
            for(String err : tc.getErrors()) {
                System.err.println("  " + err);
            }
            System.exit(1);
        }

        return ctx;
    }
}
