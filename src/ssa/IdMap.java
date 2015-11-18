package ssa;

import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

import java.util.Map;
import java.util.Set;

public class IdMap {
    private static final int START_ID = 0;
    private final Map<String, Integer> nextId;
    private final Set<String> used;

    public IdMap() {
        nextId = Maps.newHashMap();
        used = Sets.newHashSet();
    }

    public int fresh(String var) {
        if (!nextId.containsKey(var)) {
            putUnusedId(var, START_ID);
        } else {
            putUnusedId(var, id(var) + 1);
        }
        return id(var);
    }

    public void putUnusedId(String var, int startId) {
        int id = startId;
        while (used.contains(var + id)) {
            ++id;
        }
        nextId.put(var, id);
        used.add(var + id);
    }

    private int id(String var) {
        return nextId.get(var);
    }
}
