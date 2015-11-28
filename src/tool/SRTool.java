package tool;

import ast.Program;
import com.google.common.collect.Maps;
import strategy.BMC;
import strategy.Houdini;
import util.ParserUtil;

import java.io.IOException;
import java.util.NavigableMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

public class SRTool {
    private static final int OVERALL_TIMEOUT = 165000;
    private static final int TIMEOUT_SLICES = 33;
    private static final int THREADS = 4;

    public static void main(String[] args) throws IOException {
        Program program = ParserUtil.buildProgram(args[0]);
        System.out.println(computeOutcome(program));
        System.exit(0);
    }

    private static Outcome computeOutcome(Program program) {
        NavigableMap<Integer, Strategy> strategies = createOrderedStrategies(program);

        ExecutorService executor = Executors.newFixedThreadPool(THREADS);
        NavigableMap<Integer, Future<Outcome>> futures = submitVerificationTasks(executor, strategies);
        executor.shutdown();

        try {
            for (int slice = 0; slice < TIMEOUT_SLICES; ++slice) {
                long timeout = OVERALL_TIMEOUT / TIMEOUT_SLICES;
                executor.awaitTermination(timeout, TimeUnit.MILLISECONDS);

                for (int rank : futures.navigableKeySet()) {
                    Outcome outcome = queryStrategy(strategies, rank, futures.get(rank), timeout);
                    if (outcome != Outcome.UNKNOWN) {
                        return outcome;
                    }
                }
            }
        } catch (InterruptedException | ExecutionException e) {
            e.printStackTrace();
        } finally {
            executor.shutdownNow();
        }

        return Outcome.UNKNOWN;
    }

    private static Outcome queryStrategy(
        NavigableMap<Integer, Strategy> strategies, int rank, Future<Outcome> strategyFuture, long timeout)
        throws InterruptedException, ExecutionException {
        Strategy strategy = strategies.get(rank);
        strategy.decreaseTimeout(timeout);
        if (strategyFuture.isDone()) {
            return strategy.getInterpretation().apply(strategyFuture.get());
        }
        return Outcome.UNKNOWN;
    }

    private static NavigableMap<Integer, Future<Outcome>> submitVerificationTasks(
        ExecutorService executor, NavigableMap<Integer, Strategy> strategies) {
        NavigableMap<Integer, Future<Outcome>> strategyFutures = Maps.newTreeMap();
        strategies.forEach((i, s) -> strategyFutures.put(i, executor.submit(s)));
        return strategyFutures;
    }

    private static NavigableMap<Integer, Strategy> createOrderedStrategies(Program program) {
        NavigableMap<Integer, Strategy> orderedStrategies = Maps.newTreeMap();
        orderedStrategies.put(0, Houdini.basic(program, OVERALL_TIMEOUT));
        orderedStrategies.put(1, Houdini.withInvariantInference(program, OVERALL_TIMEOUT));
        orderedStrategies.put(2, new BMC(program, OVERALL_TIMEOUT));
        return orderedStrategies;
    }
}
