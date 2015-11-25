package tool;

import ast.Program;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Maps;
import strategy.Houdini;
import strategy.SoundBMC;
import strategy.UnsoundBMC;
import util.ParserUtil;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;

import static tool.Strategy.Name.HOUDINI;
import static tool.Strategy.Name.SOUND_BMC;
import static tool.Strategy.Name.UNSOUND_BMC;

public class SRTool {
    private static final int OVERALL_TIMEOUT = 160000;
    private static final int TIMEOUT_SLICES = 320;
    private static final int THREADS = 4;
    private static final Map<Strategy.Name, Function<Outcome, Outcome>> STRATEGY_OUTCOMES = defineStrategyOutcomes();

    public static void main(String[] args) throws IOException, InterruptedException {
        Program program = ParserUtil.buildProgram(args[0]);
        System.out.println(computeOutcome(program));
    }

    private static Outcome computeOutcome(Program program) throws InterruptedException {
        ExecutorService executor = Executors.newFixedThreadPool(THREADS);
        Map<Strategy, Future<Outcome>> futures = submitVerificationTasks(executor, createStrategies(program));
        executor.shutdown();

        for (int slice = 0; slice < TIMEOUT_SLICES; ++slice) {
            executor.awaitTermination(OVERALL_TIMEOUT / TIMEOUT_SLICES, TimeUnit.MILLISECONDS);
            for (Strategy strategy : futures.keySet()) {
                Outcome outcome = queryStrategy(strategy.getName(), futures.get(strategy));
                if (outcome != Outcome.UNKNOWN) {
                    executor.shutdownNow();
                    return outcome;
                }
            }
        }
        executor.shutdownNow();

        return Outcome.UNKNOWN;
    }

    private static Outcome queryStrategy(Strategy.Name strategy, Future<Outcome> strategyFuture) {
        if (strategyFuture.isDone()) {
            try {
                return STRATEGY_OUTCOMES.get(strategy).apply(strategyFuture.get());
            } catch (InterruptedException | ExecutionException e) {
            }
        }
        return Outcome.UNKNOWN;
    }

    private static Map<Strategy, Future<Outcome>> submitVerificationTasks(
        ExecutorService executor, List<Strategy> strategies) {
        Map<Strategy, Future<Outcome>> strategyFutures = Maps.newHashMap();
        strategies.forEach(s -> strategyFutures.put(s, executor.submit(s)));
        return strategyFutures;
    }

    private static List<Strategy> createStrategies(Program program) {
        return ImmutableList.of(new Houdini(program), new SoundBMC(program), new UnsoundBMC(program));
    }

    private static Map<Strategy.Name, Function<Outcome, Outcome>> defineStrategyOutcomes() {
        return ImmutableMap.of(
            // Houdini may return false negatives.
            HOUDINI, o -> o == Outcome.CORRECT ? o : Outcome.UNKNOWN,
            // Sound BMC is always reliable.
            SOUND_BMC, Function.identity(),
            // Unsound BMC may return false positives.
            UNSOUND_BMC, o -> o == Outcome.INCORRECT ? o : Outcome.UNKNOWN);
    }
}
