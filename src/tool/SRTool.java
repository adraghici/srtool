package tool;

import ast.Program;
import strategy.BMC;
import strategy.Houdini;
import util.ParserUtil;

import java.io.IOException;
import java.util.Optional;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

public class SRTool {
    private static final int TIMEOUT = 30;
    private static final int THREADS = 2;

    public static void main(String[] args) throws IOException, InterruptedException {
        Program program = ParserUtil.buildProgram(args[0]);
        System.out.println(computeOutcome(program));
    }

    private static Outcome computeOutcome(Program program) throws InterruptedException {
        Houdini houdini = new Houdini(program);
        BMC bmc = new BMC(program);

        ExecutorService executor = Executors.newFixedThreadPool(THREADS);
        Future<Outcome> bmcFuture = executor.submit(bmc);
        Future<Outcome> houdiniFuture = executor.submit(houdini);

        executor.shutdown();
        executor.awaitTermination(TIMEOUT, TimeUnit.SECONDS);
        executor.shutdownNow();

        Optional<Outcome> houdiniOutcome = Optional.empty();
        Optional<Outcome> bmcOutcome = Optional.empty();
        Outcome outcome = Outcome.UNKNOWN;

        try {
            houdiniOutcome = Optional.of(houdiniFuture.get());
        } catch (ExecutionException e) {
        } finally {
            if (houdiniOutcome.isPresent() && houdiniOutcome.get() == Outcome.CORRECT) {
                return Outcome.CORRECT;
            }
        }

        try {
            bmcOutcome = Optional.of(bmcFuture.get());
        } catch (ExecutionException e) {
        } finally {
            if (bmcOutcome.isPresent() && bmcOutcome.get() != Outcome.UNKNOWN) {
                outcome = bmcOutcome.get();
            }
        }

        return outcome;
    }
}
