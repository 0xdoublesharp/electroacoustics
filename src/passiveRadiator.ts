export interface PassiveRadiator {
  /** Total moving mass per radiator, including added mass and any modeled air load. */
  movingMassKg: number
  complianceMPerN: number
  mechanicalResistanceNsPerM: number
  sdM2: number
  quantity?: number
}

type Medium = { densityKgM3: number; soundSpeedMps: number }

export function radiatorParameters(radiator: PassiveRadiator) {
  const quantity = radiator.quantity ?? 1
  if (![radiator.movingMassKg, radiator.complianceMPerN, radiator.sdM2].every((n) => Number.isFinite(n) && n > 0) ||
      !Number.isSafeInteger(quantity) || quantity < 1 ||
      !Number.isFinite(radiator.mechanicalResistanceNsPerM) || radiator.mechanicalResistanceNsPerM < 0)
    throw new RangeError('Invalid passive radiator parameters')
  return { quantity, stiffness: 1 / radiator.complianceMPerN, areaTerm: quantity * radiator.sdM2 ** 2 }
}

function checkedStiffness(radiator: PassiveRadiator, volumeM3: number, medium: Medium): number {
  const { stiffness, areaTerm } = radiatorParameters(radiator)
  if (![volumeM3, medium.densityKgM3, medium.soundSpeedMps].every((n) => Number.isFinite(n) && n > 0))
    throw new RangeError('Invalid radiator cavity or medium')
  const result = stiffness + areaTerm * medium.densityKgM3 * medium.soundSpeedMps ** 2 / volumeM3
  if (!Number.isFinite(result) || result <= 0) throw new RangeError('Radiator stiffness exceeds numeric support')
  return result
}

/** Free suspension resonance of each passive radiator. */
export function passiveRadiatorResonanceHz(radiator: PassiveRadiator): number {
  radiatorParameters(radiator)
  const frequency = 1 / (2 * Math.PI) / Math.sqrt(radiator.movingMassKg) / Math.sqrt(radiator.complianceMPerN)
  if (!Number.isFinite(frequency)) throw new RangeError('Radiator resonance exceeds numeric support')
  return frequency
}

/** Lossless tuning of the cavity and identical passive radiators with the active cones fixed. */
export function passiveRadiatorTuningHz(radiator: PassiveRadiator, volumeM3: number, medium: Medium): number {
  const frequency = Math.sqrt(checkedStiffness(radiator, volumeM3, medium) / radiator.movingMassKg) / (2 * Math.PI)
  if (!Number.isFinite(frequency) || frequency <= 0) throw new RangeError('Radiator tuning exceeds numeric support')
  return frequency
}

/** Solve the moving mass per radiator. A negative mass change calls for removing mass. */
export function passiveRadiatorMassForTuning(radiator: PassiveRadiator, volumeM3: number, medium: Medium, targetHz: number) {
  if (!Number.isFinite(targetHz) || targetHz <= 0) throw new RangeError('Invalid radiator tuning target')
  const movingMassKg = checkedStiffness(radiator, volumeM3, medium) / (2 * Math.PI * targetHz) ** 2
  if (!Number.isFinite(movingMassKg) || movingMassKg <= 0) throw new RangeError('Radiator mass exceeds numeric support')
  return { movingMassKg, addedMassKg: movingMassKg - radiator.movingMassKg }
}
