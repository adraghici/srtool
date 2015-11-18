package tool;

import ast.ASTBuilder;
import ast.Program;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import parser.SimpleCLexer;
import parser.SimpleCParser;
import parser.SimpleCParser.ProgramContext;

import java.io.FileInputStream;
import java.io.IOException;

public class SRTool {

    public static void main(String[] args) throws IOException, InterruptedException {
        Program program = buildProgram(args[0]);
        VerificationStrategy strategy = new Houdini(program);
        System.out.println(strategy.run());
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
