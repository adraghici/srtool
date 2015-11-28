package strategy;

import ast.Program;
import tool.Outcome;
import tool.Strategy;
import util.ProcessExec;
import util.ProcessTimeoutException;
import visitor.CppGenVisitor;
import visitor.ValuesRangeVisitor;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.function.Function;

public class Cpp implements Strategy {
    private final Program program;
    private ProcessExec processExec;

    public Cpp(Program program) {
        this.program = program;
    }

    @Override
    public Outcome call() throws IOException, InterruptedException {
        // Get the min and max values.
        ValuesRangeVisitor valuesRangeVisitor = new ValuesRangeVisitor();
        program.accept(valuesRangeVisitor);

        int min = valuesRangeVisitor.getMinValue();
        int max = valuesRangeVisitor.getMaxValue();

        String cppProgram = (String) program.accept(new CppGenVisitor(min, max));

        createCppDirectory();
        writeCppProgram(cppProgram);
        compileCppProgram();

        while (true) {
            if (Thread.currentThread().isInterrupted()) {
                return Outcome.UNKNOWN;
            }

            runCppProgram();
            if (!processExec.stderr.isEmpty()) {
                // return Outcome.INCORRECT;
            }
        }
    }

    @Override
    public Name getName() {
        return Name.CPP;
    }

    @Override
    public Function<Outcome, Outcome> getInterpretation() {
        return outcome -> outcome == Outcome.INCORRECT ? outcome : Outcome.UNKNOWN;
    }

    private void createCppDirectory() throws IOException, InterruptedException {
        processExec = new ProcessExec("mkdir", "-p", "c++");
        try {
            processExec.execute("", Integer.MAX_VALUE);
        } catch (ProcessTimeoutException e) {

        }
    }

    private void writeCppProgram(String cppProgram) throws IOException {
        try (Writer writer = new BufferedWriter(new OutputStreamWriter(
            new FileOutputStream("c++/main.cpp"), "utf-8"))) {
            writer.write(cppProgram);
        }
    }

    private void compileCppProgram() throws IOException, InterruptedException {
        processExec = new ProcessExec("g++", "c++/main.cpp", "-o", "c++/main");
        try {
            processExec.execute("", Integer.MAX_VALUE);
        } catch (ProcessTimeoutException e) {

        }
    }

    private void runCppProgram() throws IOException, InterruptedException {
        processExec = new ProcessExec("./c++/main");
        try {
            processExec.execute("", Integer.MAX_VALUE);
        } catch (ProcessTimeoutException e) {

        }
    }
}
