import type { CircuitInput, ThieleSmallDriver } from './circuit.js'

export function driverMotor(driver: ThieleSmallDriver, medium: CircuitInput['medium']) {
  const omega = 2 * Math.PI * driver.fsHz
  const cms = driver.vasM3 / (medium.densityKgM3 * medium.soundSpeedMps ** 2 * driver.sdM2 ** 2)
  const mms = 1 / (omega ** 2 * cms)
  const rms = omega * mms / driver.qms
  const blSquared = omega * mms * driver.reOhms / driver.qes
  return { cms, mms, rms, blSquared }
}
