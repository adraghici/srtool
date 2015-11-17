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

import java.io.FileInputStream;
import java.io.IOException;

public class SRTool {
    private static final int TIMEOUT = 30000;

    public static void main(String[] args) throws IOException, InterruptedException {
        SMTModel smtModel = new Houdini(buildProgram(args[0])).run();

        ProcessExec process = new ProcessExec("z3", "-smt2", "-in");
        String queryResult = "";
        try {
            queryResult = process.execute(smtModel.getCode(), TIMEOUT);
            System.err.println(queryResult);
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

    private static Program buildProgram(String filename) throws IOException {
        ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filename));
        ProgramContext ctx = getProgramContext(input);
        Program program = ASTBuilder.build((ProgramContext) ctx.getChild(0).getParent());
        return program;
    }

    private static ProgramContext getProgramContext(ANTLRInputStream input) {
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
            System.err.println("Errors were detected when typechecking the file:");
            for(String err : tc.getErrors()) {
                System.err.println("  " + err);
            }
            System.exit(1);
        }

        return ctx;
    }
}
