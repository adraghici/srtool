package util;

import ast.ASTBuilder;
import ast.Program;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import parser.SimpleCLexer;
import parser.SimpleCParser;
import tool.Typechecker;

import java.io.FileInputStream;
import java.io.IOException;

public class ParserUtil {

    public static Program buildProgram(String filename) throws IOException {
        ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filename));
        SimpleCParser.ProgramContext
            programTree = (SimpleCParser.ProgramContext) ParserUtil.createProgramContext(input).getChild(0).getParent();
        return ASTBuilder.build(programTree);
    }

    public static SimpleCParser.ProgramContext createProgramContext(ANTLRInputStream input) {
        SimpleCLexer lexer = new SimpleCLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        SimpleCParser parser = new SimpleCParser(tokens);
        SimpleCParser.ProgramContext ctx = parser.program();

        if (parser.getNumberOfSyntaxErrors() > 0) {
            System.exit(1);
        }

        Typechecker typechecker = new Typechecker();
        typechecker.visit(ctx);
        typechecker.resolve();

        if (typechecker.hasErrors()) {
            System.err.println(
                "Errors were detected when typechecking the file:" + String.join(" ", typechecker.getErrors()));
            System.exit(1);
        }

        return ctx;
    }
}
