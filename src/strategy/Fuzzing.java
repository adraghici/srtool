package strategy;

import ast.Program;
import util.ProcessExec;
import visitor.FuzzingVisitor;
import visitor.ValuesRangeVisitor;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.util.concurrent.TimeoutException;
import java.util.function.Function;

public class Fuzzing implements Strategy {
    private final Program program;
    private ProcessExec processExec;

    public Fuzzing(Program program) {
        this.program = program;
    }

    @Override
    public Outcome call() throws IOException, InterruptedException {
        // Get the min and max values.
        ValuesRangeVisitor valuesRangeVisitor = new ValuesRangeVisitor();
        program.accept(valuesRangeVisitor);

        int min = valuesRangeVisitor.getMinValue();
        int max = valuesRangeVisitor.getMaxValue();
        int seed = 0;

        if (min == max) {
            min = min / 2;
        }

        // Heuristic: random values chosen will be between min and 2 * max.
        String cppProgram = (String) program.accept(new FuzzingVisitor(min, 2 * max));

        cleanCppDirectory();
        createCppDirectory();
        writeCppProgram(cppProgram);
        compileCppProgram();

        while (true) {
            if (Thread.currentThread().isInterrupted()) {
                return Outcome.UNKNOWN;
            }

            // Run the C++ executable (if present) with an increasing seed.
            runCppProgram(seed++);

            if (!processExec.stderr.isEmpty()) {
                return Outcome.INCORRECT;
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

    @Override
    public void decreaseTimeout(long difference) { }

    private void createCppDirectory() throws IOException, InterruptedException {
        processExec = new ProcessExec("mkdir", "-p", "c++");
        try {
            processExec.execute("", Integer.MAX_VALUE);
        } catch (TimeoutException e) {

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
        } catch (TimeoutException e) {

        }
    }

    private void runCppProgram(int seed) throws IOException, InterruptedException {
        processExec = new ProcessExec("./c++/main", Integer.toString(seed));
        try {
            processExec.execute("", Integer.MAX_VALUE);
        } catch (TimeoutException e) {

        }
    }

    private void cleanCppDirectory() throws IOException, InterruptedException {
        processExec = new ProcessExec("rm", "-rf", "c++");
        try {
            processExec.execute("", Integer.MAX_VALUE);
        } catch (TimeoutException e) {

        }
    }
}
