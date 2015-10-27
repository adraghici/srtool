package tool;

import com.google.common.collect.Maps;

import java.util.Map;

public class SSAMap {
    private static final Integer START_ID = 0;
    private final Map<String, Integer> nextID;

    public SSAMap() {
        this.nextID = Maps.newHashMap();
    }

    public int fresh(String var) {
        if (!nextID.containsKey(var)) {
            nextID.put(var, START_ID);
        } else {
            nextID.put(var, id(var) + 1);
        }
        return id(var);
    }

    private int id(String var) {
        return nextID.get(var);
    }
}
