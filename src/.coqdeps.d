definition.vo definition.glob definition.v.beautified: definition.v
definition.vio: definition.v
infra.vo infra.glob infra.v.beautified: infra.v definition.vo
infra.vio: infra.v definition.vio
subtyping.vo subtyping.glob subtyping.v.beautified: subtyping.v infra.vo
subtyping.vio: subtyping.v infra.vio
typesafety.vo typesafety.glob typesafety.v.beautified: typesafety.v subtyping.vo
typesafety.vio: typesafety.v subtyping.vio
decidability.vo decidability.glob decidability.v.beautified: decidability.v subtyping.vo
decidability.vio: decidability.v subtyping.vio
amber_part_1.vo amber_part_1.glob amber_part_1.v.beautified: amber_part_1.v definition.vo infra.vo subtyping.vo
amber_part_1.vio: amber_part_1.v definition.vio infra.vio subtyping.vio
amber_part_2.vo amber_part_2.glob amber_part_2.v.beautified: amber_part_2.v amber_part_1.vo decidability.vo
amber_part_2.vio: amber_part_2.v amber_part_1.vio decidability.vio
