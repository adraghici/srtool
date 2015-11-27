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
    private static final int TIMEOUT_SLICES = 40;
    private static final int THREADS = 4;

    public static void main(String[] args) throws IOException {
        Program program = ParserUtil.buildProgram(args[0]);
        System.out.println(computeOutcome(program));
    }

    private static Outcome computeOutcome(Program program) {
        NavigableMap<Integer, Strategy> strategies = createOrderedStrategies(program);

        ExecutorService executor = Executors.newFixedThreadPool(THREADS);
        NavigableMap<Integer, Future<Outcome>> futures = submitVerificationTasks(executor, strategies);
        executor.shutdown();

        try {
            for (int slice = 0; slice < TIMEOUT_SLICES; ++slice) {
                executor.awaitTermination(OVERALL_TIMEOUT / TIMEOUT_SLICES, TimeUnit.MILLISECONDS);
                for (int rank : futures.navigableKeySet()) {
                    Outcome outcome = queryStrategy(strategies, rank, futures.get(rank));
                    if (outcome != Outcome.UNKNOWN) {
                        return outcome;
                    }
                }
            }
        } catch (InterruptedException e) {
        } finally {
            executor.shutdownNow();
        }

        return Outcome.UNKNOWN;
    }

    private static Outcome queryStrategy(
        NavigableMap<Integer, Strategy> strategies, int rank, Future<Outcome> strategyFuture) {
        if (strategyFuture.isDone()) {
            try {
                return strategies.get(rank).getInterpretation().apply(strategyFuture.get());
            } catch (InterruptedException | ExecutionException e) {
            }
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
        orderedStrategies.put(0, Houdini.basic(program));
        orderedStrategies.put(1, Houdini.withInvariantInferece(program));
        orderedStrategies.put(2, new BMC(program));
        return orderedStrategies;
    }
}
