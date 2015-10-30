package tool;

import com.google.common.collect.Maps;

import java.util.Map;

public class IdMap {
    private static final int START_ID = 0;
    private final Map<String, Integer> nextId;

    public IdMap() {
        nextId = Maps.newHashMap();
    }

    public int fresh(String var) {
        if (!nextId.containsKey(var)) {
            nextId.put(var, START_ID);
        } else {
            nextId.put(var, id(var) + 1);
        }
        return id(var);
    }

    private int id(String var) {
        return nextId.get(var);
    }
}
